#include <algorithm>
#include <deque>
#include <iostream>
#include <string>
#include <vector>
#include <queue>
#include <map>
#include <unordered_set>
#include <iterator>
#include <sstream>
#include <memory>
#include <stdexcept>
#include <utility>
#include <set>

//  std::make_unique will be available since c++14
//  Implementation was taken from http://herbsutter.com/gotw/_102/
template<typename T, typename... Args>
std::unique_ptr<T> make_unique(Args&&... args)
{
  return std::unique_ptr<T>(new T(std::forward<Args>(args)...));
}

template<class Visitor, class Graph, class Vertex>
void BreadthFirstSearch(Vertex origin_vertex, const Graph& graph, Visitor visitor)
{
  std::unordered_set<Vertex> used_vertex;
  std::queue <Vertex> vertices;
  vertices.push(origin_vertex);
  visitor.DiscoverVertex(origin_vertex);
  used_vertex.insert(origin_vertex);

  while (!vertices.empty())
  {
    visitor.ExamineVertex(vertices.front());
    for (auto edge: graph.OutgoingEdges(vertices.front()))
    {
      if (!used_vertex.count(GetTarget(edge)))
      {
        visitor.ExamineEdge(edge);
        visitor.DiscoverVertex(GetTarget(edge));
        vertices.push(GetTarget(edge));
        used_vertex.insert(GetTarget(edge));
      }
    }
    vertices.pop();
  }
}

// See "Visitor Event Points" on
// http://www.boost.org/doc/libs/1_57_0/libs/graph/doc/breadth_first_search.html
template<class Vertex, class Edge>
class BfsVisitor
{
public:
  virtual void DiscoverVertex(Vertex /*vertex*/) {}
  virtual void ExamineEdge(const Edge& /*edge*/) {}
  virtual void ExamineVertex(Vertex /*vertex*/) {}
  virtual ~BfsVisitor() {}
};

struct AutomatonNode
{
  AutomatonNode(): suffix_link(nullptr), terminal_link(nullptr)
  {
  }

  // Stores tree structure of nodes
  std::map<char, AutomatonNode> trie_transitions;
  // Stores pointers to the elements of trie_transitions
  std::map<char, AutomatonNode*> automaton_transitions;

  AutomatonNode* suffix_link;
  AutomatonNode* terminal_link;
  std::vector<size_t> matched_string_ids;
};

// Returns nullptr if there is no such transition
AutomatonNode* GetTrieTransition(AutomatonNode* node, char character)
{
  auto trie_iterator = node->trie_transitions.find(character);
  if (trie_iterator != node->trie_transitions.end())
  {
    return &trie_iterator->second;
  }
  else
  {
    return nullptr;
  }
}

// Performs transition in automaton
AutomatonNode* GetNextNode(AutomatonNode* node, AutomatonNode* root, char character)
{
  auto automaton_iterator = node->automaton_transitions.find(character);
  if (automaton_iterator !=
          node->automaton_transitions.end())
  {
    return automaton_iterator->second;
  }

  AutomatonNode* result;
  auto trie_iterator = node->trie_transitions.find(character);
  if (trie_iterator != node->trie_transitions.end())
  {
    result = &trie_iterator->second;
  }
  else
  {
    if (node == root)
    {
      result = root;
    }
    else
    {
      result = GetNextNode(node->suffix_link, root, character);
    }
  }

  node->automaton_transitions[character] = result;

  return result;
}

class AutomatonGraph
{
public:
  struct Edge
  {
    Edge(AutomatonNode* source,
           AutomatonNode* target,
           char character):
    source(source),
    target(target),
    character(character)
    {}

    AutomatonNode *source;
    AutomatonNode *target;
    char character;
  };

  // Returns edges corresponding to all trie transitions from vertex
  std::vector<Edge> OutgoingEdges(AutomatonNode* vertex) const
  {
    std::vector<Edge> edges;
    for (auto& edge: vertex->trie_transitions)
    {
      edges.emplace_back(vertex, &edge.second, edge.first);
    }
    return edges;
  }
};

AutomatonNode* GetTarget(const AutomatonGraph::Edge& edge)
{
  return edge.target;
}

class SuffixLinkCalculator:
public BfsVisitor<AutomatonNode*, AutomatonGraph::Edge>
{
public:
  explicit SuffixLinkCalculator(AutomatonNode* root):
      root_(root) {}

  void ExamineVertex(AutomatonNode* ) /*override*/ {}

  void ExamineEdge(const AutomatonGraph::Edge& edge) /*override*/
  {
    if (edge.target->suffix_link)
    {
      return;
    }

    edge.target->suffix_link = (edge.source == root_ ? root_ :
                               GetNextNode(edge.source->suffix_link, root_, edge.character));
  }

private:
    AutomatonNode *root_;
};

class TerminalLinkCalculator:
public BfsVisitor<AutomatonNode*, AutomatonGraph::Edge>
{
public:
  explicit TerminalLinkCalculator(AutomatonNode* root):
      root_(root)
  {}

  void DiscoverVertex(AutomatonNode* node) /*override*/
  {
    if (node->terminal_link || node == root_)
    {
      return;
    }

    if (!node->suffix_link->matched_string_ids.empty())
    {
      node->terminal_link = node->suffix_link;
    }
    else
    {
      node->terminal_link = node->suffix_link->terminal_link;
    }
  }

private:
    AutomatonNode* root_;
};

class NodeReference
{
public:
  NodeReference():
      node_(nullptr),
      root_(nullptr)
  {}

  NodeReference(AutomatonNode* node, AutomatonNode* root):
      node_(node),
      root_(root)
  {}

  NodeReference Next(char character) const
  {
    return NodeReference(GetNextNode(node_, root_, character), root_);
  }

  NodeReference TerminalLink() const
  {
    return NodeReference(node_->terminal_link, root_);
  }

  std::vector<size_t> MatchedStringIds() const
  {
    return node_->matched_string_ids;
  }

  explicit operator bool() const
  {
    return node_ != nullptr;
  }

  bool operator== (NodeReference other) const
  {
    return node_ == other.node_;
  }

private:
  AutomatonNode* node_;
  AutomatonNode* root_;
};

using std::rel_ops::operator !=;

class AutomatonBuilder;

class Automaton
{
public:
    Automaton() = default;


    NodeReference GetRoot()
    {
      return NodeReference(&root_, &root_);
    }

    // Calls on_match(string_id) for every string ending at
    // this node, i.e. collects all string ids reachable by
    // terminal links.
    template <class Callback>
    void GenerateMatches(NodeReference node, Callback on_match)
    {
        while (node)
        {
          for (size_t string_id: node.MatchedStringIds())
          {
            on_match(string_id);
          }
          node = node.TerminalLink();
        }
    }

private:
    AutomatonNode root_;

    Automaton(const Automaton&) = delete;
    Automaton& operator=(const Automaton&) = delete;

    friend class AutomatonBuilder;
};

class AutomatonBuilder
{
public:
  void Add(const std::string& string, size_t id)
  {
    words_.push_back(string);
    ids_.push_back(id);
  }

  std::unique_ptr<Automaton> Build ()
  {
    auto automaton = make_unique<Automaton>();
    BuildTrie(words_, ids_, automaton.get());
    BuildSuffixLinks(automaton.get());
    BuildTerminalLinks(automaton.get());
    return automaton;
  }

private:
  void BuildTrie(const std::vector<std::string>& words,
                  const std::vector<size_t>& ids,
                  Automaton* automaton)
  {
    for (size_t i = 0; i < words.size(); ++i)
    {
      AddString(&automaton->root_, words[i], ids[i]);
    }
  }

  static void AddString(AutomatonNode* root, const std::string& string, size_t string_id)
  {
    AutomatonNode* node = root;
    for (char character: string)
    {
      node = &(node->trie_transitions[character]);
    }
    node->matched_string_ids.push_back(string_id);
  }


  static void BuildSuffixLinks(Automaton* automaton)
  {
    automaton->root_.suffix_link = &automaton->root_;
    BreadthFirstSearch(&automaton->root_, AutomatonGraph(),
                         SuffixLinkCalculator(&automaton->root_));
  }

  static void BuildTerminalLinks(Automaton* automaton)
  {
    automaton->root_.terminal_link = nullptr;
    BreadthFirstSearch(&automaton->root_, AutomatonGraph(),
                         TerminalLinkCalculator(&automaton->root_));
  }

  std::vector<size_t> ids_;
  std::vector<std::string> words_;
};

std::vector<std::string> Split(const std::string& string, char wildcard)
{
  std::vector<std::string> result;

  auto previous_entry = string.begin();
  auto next_entry = string.begin();

  while (previous_entry != string.end())
    {
      next_entry = std::find_if(previous_entry, string.end(),
        [wildcard](char symbol) -> bool
        {
          return symbol == wildcard;
        }
      );
      result.emplace_back(previous_entry, next_entry);
      previous_entry = (next_entry == string.end() ? string.end() : next_entry + 1);
    }

  if (string.back() == wildcard)
    result.push_back ("");

  return result;
}

// Wildcard is a character that may be substituted
// for any of all possible characters
class WildcardMatcher
{
public:
  WildcardMatcher():
      number_of_words_(0),
      pattern_length_(0)
  {}

  void Init(const std::string& pattern, char wildcard)
  {
    AutomatonBuilder builder;
    number_of_words_ = 0;
    pattern_length_ = pattern.size();

    auto split_pattern = Split(pattern, wildcard);

    size_t string_id = 0;
    for (const auto &string : split_pattern)
    {
      string_id += string.size();
      builder.Add(string, string_id);
      ++number_of_words_;
      ++string_id;
    }

    aho_corasick_automaton_ = builder.Build();
    Reset();
  }

  void InitWordsOccurences()
  {
    words_occurrences_by_position_.assign(pattern_length_ + 1, 0);

    // Initing by empty strings in root

    auto& words_occurences_by_position_local = words_occurrences_by_position_;
    size_t pattern_length_local = pattern_length_;

    aho_corasick_automaton_->GenerateMatches(aho_corasick_automaton_->GetRoot(),
        [&words_occurences_by_position_local, pattern_length_local] (size_t offset)
        {
          ++words_occurences_by_position_local[pattern_length_local - offset];
        });
  }

  // Resets matcher to start scanning new stream
  void Reset()
  {
    InitWordsOccurences();
    state_  = aho_corasick_automaton_->GetRoot();
  }

  // Scans new character and calls on_match() if
  // suffix of scanned characters matches pattern
  template<class Callback>
  void Scan(char character, Callback on_match)
  {
    state_ = state_.Next(character);

    words_occurrences_by_position_.push_back(0);

    auto& words_occurences_by_position_local = words_occurrences_by_position_;
    size_t pattern_length_local = pattern_length_;

    aho_corasick_automaton_->GenerateMatches(state_,
        [&words_occurences_by_position_local, pattern_length_local] (size_t offset)
        {
          ++words_occurences_by_position_local[pattern_length_local - offset + 1];
        });

    words_occurrences_by_position_.pop_front();

    if (words_occurrences_by_position_.front() == number_of_words_)
    {
      on_match();
    }
  }

private:
  // Storing only O(|pattern|) elements allows us
  // to consume only O(|pattern|) memory for matcher
  std::deque<size_t> words_occurrences_by_position_;
  NodeReference state_;
  size_t number_of_words_;
  size_t pattern_length_;
  std::unique_ptr<Automaton> aho_corasick_automaton_;
};

std::string ReadString(std::istream& input_stream)
{
  std::string str;
  input_stream >> str;
  return str;
}

// Returns positions of the first character of every match
std::vector<size_t> FindFuzzyMatches(const std::string& patternWithWildcards,
                                   const std::string& text, char wildcard)
{
  WildcardMatcher matcher;
  matcher.Init(patternWithWildcards, wildcard);
  std::vector<size_t> occurrences;
  for (int offset = 0; offset < static_cast<int>(text.size()); ++offset)
  {
    matcher.Scan(text[offset],
                [&occurrences, offset, &patternWithWildcards]
                    {
                      occurrences.push_back(offset + 1 - patternWithWildcards.size());
                    });
  }
  return occurrences;
}

void Print(const std::vector<size_t>& sequence, std::ostream& output_stream)
{
  output_stream << sequence.size() << "\n";
  for (const auto& element: sequence)
  {
    output_stream << element << " ";
  }
  output_stream << "\n";
}

int main()
{
  const char wildcard = '?';
  const std::string patternWithWildcards = ReadString(std::cin);
  const std::string text = ReadString(std::cin);
  Print(FindFuzzyMatches(patternWithWildcards, text, wildcard), std::cout);
  return 0;
}

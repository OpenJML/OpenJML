OPENJML=PATH_TO_OPENJML_openjml-ubuntu-20.04-0.17.0-alpha-15_bin
FLAG=-esc

echo "$OPENJML $FLAG ./src/CompositeCollection.java ./src/IteratorChain.java ./src/EmptyIterator.java ./src/CollectionUtils.java ./src/UnmodifiableList.java -progress > CompositeCollection.java.log "
$OPENJML $FLAG ./src/CompositeCollection.java ./src/IteratorChain.java ./src/EmptyIterator.java ./src/CollectionUtils.java ./src/UnmodifiableList.java -progress > CompositeCollection.java.log 
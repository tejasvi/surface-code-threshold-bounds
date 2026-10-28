import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6068 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6068 = true := by
  decide +kernel

theorem tot6068 : totK PA10K2 A10K2.t6068 = [0, 442305784794, 1730423060259, 1946029006981, 527220926615, 31362375073, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6069 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6069 = true := by
  decide +kernel

theorem tot6069 : totK PA10K2 A10K2.t6069 = [0, 186400957300, 1153250435256, 2097993039317, 1293169356215, 260626731781, 20070762815, 0, 0, 0] := by
  decide +kernel

theorem rows6070 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6070 = true := by
  decide +kernel

theorem tot6070 : totK PA10K2 A10K2.t6070 = [0, 113327924872, 746822346190, 1840825653602, 1607281629684, 341287190246, 10709677363, 0, 0, 0] := by
  decide +kernel

theorem rows6071 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6071 = true := by
  decide +kernel

theorem tot6071 : totK PA10K2 A10K2.t6071 = [0, 407175321486, 1725762483949, 1964990650832, 554644566253, 32054330997, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

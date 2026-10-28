import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5200 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5200 = true := by
  decide +kernel

theorem tot5200 : totK PA10K2 A10K2.t5200 = [0, 0, 482375222045, 1824612364046, 1939462230464, 522782700337, 31987755669, 0, 0, 0] := by
  decide +kernel

theorem rows5201 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5201 = true := by
  decide +kernel

theorem tot5201 : totK PA10K2 A10K2.t5201 = [0, 0, 530031261579, 1939921325921, 1923009682565, 452727441964, 13149912228, 0, 0, 0] := by
  decide +kernel

theorem rows5202 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5202 = true := by
  decide +kernel

theorem tot5202 : totK PA10K2 A10K2.t5202 = [0, 0, 534446173463, 1818235953385, 1802886172406, 503097498386, 32470943963, 0, 0, 0] := by
  decide +kernel

theorem rows5203 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5203 = true := by
  decide +kernel

theorem tot5203 : totK PA10K2 A10K2.t5203 = [0, 0, 451267901403, 1692490374892, 1881963655428, 579879449646, 50267370225, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

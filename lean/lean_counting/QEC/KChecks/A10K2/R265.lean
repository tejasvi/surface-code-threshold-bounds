import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1060 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1060 = true := by
  decide +kernel

theorem tot1060 : totK PA10K2 A10K2.t1060 = [0, 0, 512933326219, 1845988455808, 1755080154211, 474060924043, 30831673886, 0, 0, 0] := by
  decide +kernel

theorem rows1061 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1061 = true := by
  decide +kernel

theorem tot1061 : totK PA10K2 A10K2.t1061 = [0, 478610618287, 1618027605531, 1928080842158, 847971644294, 85992672972, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1062 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1062 = true := by
  decide +kernel

theorem tot1062 : totK PA10K2 A10K2.t1062 = [0, 291093484992, 1475656776019, 2109327970290, 846509451434, 65194457115, 0, 0, 0, 0] := by
  decide +kernel

theorem rows1063 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1063 = true := by
  decide +kernel

theorem tot1063 : totK PA10K2 A10K2.t1063 = [0, 537828726768, 1886800751465, 2014982753864, 603834680353, 41067685503, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

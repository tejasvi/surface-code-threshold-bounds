import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4248 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4248 = true := by
  decide +kernel

theorem tot4248 : totK PA10K2 A10K2.t4248 = [0, 305330155506, 1529223438472, 2156662523099, 879904343120, 76381823220, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4249 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4249 = true := by
  decide +kernel

theorem tot4249 : totK PA10K2 A10K2.t4249 = [0, 112276258614, 854929174912, 2109387201050, 1521094887311, 265297957570, 6904928264, 0, 0, 0] := by
  decide +kernel

theorem rows4250 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4250 = true := by
  decide +kernel

theorem tot4250 : totK PA10K2 A10K2.t4250 = [0, 481993654812, 1832838732019, 2084878009307, 677990497736, 38658382994, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4251 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4251 = true := by
  decide +kernel

theorem tot4251 : totK PA10K2 A10K2.t4251 = [0, 67599317612, 771283211829, 2115878195494, 1754194637173, 314658692127, 7047025452, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

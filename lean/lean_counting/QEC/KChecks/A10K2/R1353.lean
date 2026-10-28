import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5412 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5412 = true := by
  decide +kernel

theorem tot5412 : totK PA10K2 A10K2.t5412 = [0, 0, 321323071444, 1064421144320, 1531129275110, 1451869954119, 505712936893, 35764095907, 0, 0] := by
  decide +kernel

theorem rows5413 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5413 = true := by
  decide +kernel

theorem tot5413 : totK PA10K2 A10K2.t5413 = [0, 0, 433689543281, 1767569429050, 1995856000861, 557519509717, 32731286466, 0, 0, 0] := by
  decide +kernel

theorem rows5414 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5414 = true := by
  decide +kernel

theorem tot5414 : totK PA10K2 A10K2.t5414 = [0, 0, 114797664464, 982869469098, 2107978294624, 1409239504229, 282715386637, 20340910120, 0, 0] := by
  decide +kernel

theorem rows5415 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5415 = true := by
  decide +kernel

theorem tot5415 : totK PA10K2 A10K2.t5415 = [0, 0, 87893776733, 721133264819, 1906857455693, 1642900426189, 337973203284, 11427838733, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5472 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5472 = true := by
  decide +kernel

theorem tot5472 : totK PA10K2 A10K2.t5472 = [0, 557742759892, 1781663946267, 1622355831223, 593845000274, 228212921098, 30195939839, 0, 0, 0] := by
  decide +kernel

theorem rows5473 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5473 = true := by
  decide +kernel

theorem tot5473 : totK PA10K2 A10K2.t5473 = [0, 93946978215, 952334964087, 2001892353064, 1340271842727, 321162693779, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows5474 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5474 = true := by
  decide +kernel

theorem tot5474 : totK PA10K2 A10K2.t5474 = [0, 299638544946, 1187099224031, 1861321716462, 1193781392891, 197640771381, 5460492893, 0, 0, 0] := by
  decide +kernel

theorem rows5475 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5475 = true := by
  decide +kernel

theorem tot5475 : totK PA10K2 A10K2.t5475 = [0, 465631835236, 1805285841891, 2023331606508, 553282657111, 19117496088, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

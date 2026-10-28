import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4124 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4124 = true := by
  decide +kernel

theorem tot4124 : totK PA10K2 A10K2.t4124 = [0, 320163320273, 1125237066907, 1551208059438, 1326352123814, 509041288312, 48886019071, 0, 0, 0] := by
  decide +kernel

theorem rows4125 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4125 = true := by
  decide +kernel

theorem tot4125 : totK PA10K2 A10K2.t4125 = [0, 547276774139, 1810392053801, 1847641810400, 503121585466, 31923522143, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4126 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4126 = true := by
  decide +kernel

theorem tot4126 : totK PA10K2 A10K2.t4126 = [0, 0, 732484128711, 2107913419476, 1624063939212, 365198157966, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows4127 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4127 = true := by
  decide +kernel

theorem tot4127 : totK PA10K2 A10K2.t4127 = [0, 212919441758, 1054827472320, 1932936627488, 1287018956910, 209992075010, 5460492893, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

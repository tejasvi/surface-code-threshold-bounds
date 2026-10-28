import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7728 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7728 = true := by
  decide +kernel

theorem tot7728 : totK PA10K2 A10K2.t7728 = [0, 0, 0, 187008388615, 1229715621822, 2182645474034, 1186280982511, 180440325789, 7237400819, 0] := by
  decide +kernel

theorem rows7729 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7729 = true := by
  decide +kernel

theorem tot7729 : totK PA10K2 A10K2.t7729 = [0, 0, 0, 390380463019, 1639464794678, 2128919145079, 785720606233, 67672580206, 0, 0] := by
  decide +kernel

theorem rows7730 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7730 = true := by
  decide +kernel

theorem tot7730 : totK PA10K2 A10K2.t7730 = [0, 0, 0, 433828855635, 1834370608904, 2208309749033, 679134748962, 31503120867, 0, 0] := by
  decide +kernel

theorem rows7731 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7731 = true := by
  decide +kernel

theorem tot7731 : totK PA10K2 A10K2.t7731 = [0, 0, 542450728586, 1869335441347, 1771497925162, 499072293075, 113634400626, 26048048901, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

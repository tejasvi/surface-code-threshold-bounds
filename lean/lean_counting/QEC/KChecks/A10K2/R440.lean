import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1760 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1760 = true := by
  decide +kernel

theorem tot1760 : totK PA10K2 A10K2.t1760 = [0, 0, 0, 491445703052, 1820900671653, 1921028521118, 477372945811, 32470943963, 0, 0] := by
  decide +kernel

theorem rows1761 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1761 = true := by
  decide +kernel

theorem tot1761 : totK PA10K2 A10K2.t1761 = [0, 0, 0, 655205426518, 2073189834720, 1700169687030, 291005218020, 10732792974, 0, 0] := by
  decide +kernel

theorem rows1762 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1762 = true := by
  decide +kernel

theorem tot1762 : totK PA10K2 A10K2.t1762 = [0, 0, 0, 300096290637, 1511607982768, 2087148003854, 652110333053, 37324864939, 0, 0] := by
  decide +kernel

theorem rows1763 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1763 = true := by
  decide +kernel

theorem tot1763 : totK PA10K2 A10K2.t1763 = [0, 0, 213371739588, 425599783614, 811940682410, 1734391355414, 1190586605487, 218133052917, 6354482628, 0] := by
  decide +kernel

end QECKChecks.A10K2

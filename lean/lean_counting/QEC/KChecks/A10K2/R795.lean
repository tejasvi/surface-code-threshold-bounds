import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3180 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3180 = true := by
  decide +kernel

theorem tot3180 : totK PA10K2 A10K2.t3180 = [0, 576047241256, 1851025920792, 1786951136133, 527628622890, 31941609474, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3181 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3181 = true := by
  decide +kernel

theorem tot3181 : totK PA10K2 A10K2.t3181 = [0, 0, 1010810577629, 2364591409798, 1153689604007, 94662425450, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3182 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3182 = true := by
  decide +kernel

theorem tot3182 : totK PA10K2 A10K2.t3182 = [0, 475019784619, 1566139813933, 1856460436125, 914805402479, 171718886163, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows3183 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3183 = true := by
  decide +kernel

theorem tot3183 : totK PA10K2 A10K2.t3183 = [0, 310203719009, 1498911401528, 2196132067808, 925887494169, 73849829118, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

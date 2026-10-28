import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6296 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6296 = true := by
  decide +kernel

theorem tot6296 : totK PA10K2 A10K2.t6296 = [105921830056, 137310103967, 676423671564, 1965796739233, 1396161005594, 259417048368, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows6297 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6297 = true := by
  decide +kernel

theorem tot6297 : totK PA10K2 A10K2.t6297 = [405106491921, 1757882733910, 2166571245285, 812715217573, 70896342421, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6298 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6298 = true := by
  decide +kernel

theorem tot6298 : totK PA10K2 A10K2.t6298 = [312105522993, 1249796239205, 1964979471771, 1302408636034, 276112177915, 19398939937, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6299 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6299 = true := by
  decide +kernel

theorem tot6299 : totK PA10K2 A10K2.t6299 = [501108923794, 1861945062822, 1969041089601, 559696281333, 32780555804, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

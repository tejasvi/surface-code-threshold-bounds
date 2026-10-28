import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2188 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2188 = true := by
  decide +kernel

theorem tot2188 : totK PA10K2 A10K2.t2188 = [319364795913, 1475079850984, 2189728594954, 976558859344, 88936740673, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2189 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2189 = true := by
  decide +kernel

theorem tot2189 : totK PA10K2 A10K2.t2189 = [0, 604811289320, 2065487125581, 1963491780915, 453011566394, 13814447077, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2190 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2190 = true := by
  decide +kernel

theorem tot2190 : totK PA10K2 A10K2.t2190 = [0, 436878214733, 1693811460231, 2023776850547, 757064835079, 69753583762, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2191 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2191 = true := by
  decide +kernel

theorem tot2191 : totK PA10K2 A10K2.t2191 = [0, 529417277059, 1928171808379, 1963943287516, 445958196492, 11933990244, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

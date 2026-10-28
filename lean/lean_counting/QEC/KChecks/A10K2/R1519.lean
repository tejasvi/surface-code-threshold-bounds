import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6076 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6076 = true := by
  decide +kernel

theorem tot6076 : totK PA10K2 A10K2.t6076 = [0, 0, 473824478388, 1841421733498, 1833864349449, 443702342656, 25574856276, 0, 0, 0] := by
  decide +kernel

theorem rows6077 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6077 = true := by
  decide +kernel

theorem tot6077 : totK PA10K2 A10K2.t6077 = [0, 0, 295331246169, 1415347768991, 2191193431730, 983173201522, 92830772229, 0, 0, 0] := by
  decide +kernel

theorem rows6078 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6078 = true := by
  decide +kernel

theorem tot6078 : totK PA10K2 A10K2.t6078 = [0, 0, 285514943267, 1247042430849, 1860694624966, 1104733437781, 209897597623, 7007974415, 0, 0] := by
  decide +kernel

theorem rows6079 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6079 = true := by
  decide +kernel

theorem tot6079 : totK PA10K2 A10K2.t6079 = [0, 0, 524321158356, 1939832931266, 1847588671140, 364986083778, 11531959710, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

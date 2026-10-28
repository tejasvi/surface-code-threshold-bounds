import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6008 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6008 = true := by
  decide +kernel

theorem tot6008 : totK PA10K2 A10K2.t6008 = [0, 460697748264, 1684374386072, 1874094404794, 702848361652, 69293176671, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6009 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6009 = true := by
  decide +kernel

theorem tot6009 : totK PA10K2 A10K2.t6009 = [0, 289230506492, 1411095725762, 2103554660074, 852274302850, 60535023068, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6010 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6010 = true := by
  decide +kernel

theorem tot6010 : totK PA10K2 A10K2.t6010 = [0, 297392362862, 1219427293268, 1855890072894, 1128360765016, 219922360482, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows6011 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6011 = true := by
  decide +kernel

theorem tot6011 : totK PA10K2 A10K2.t6011 = [0, 295757175837, 1456944452847, 2203216624306, 1007781412438, 96548190634, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

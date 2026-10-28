import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2912 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2912 = true := by
  decide +kernel

theorem tot2912 : totK PA10K2 A10K2.t2912 = [0, 500634049400, 1923977107773, 2020380673799, 578478039650, 32507549022, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2913 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2913 = true := by
  decide +kernel

theorem tot2913 : totK PA10K2 A10K2.t2913 = [289498769530, 1058329186342, 1584321551795, 1442619533400, 565106323794, 50555834002, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2914 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2914 = true := by
  decide +kernel

theorem tot2914 : totK PA10K2 A10K2.t2914 = [436450538801, 1712265537024, 2014688895108, 659074115884, 38414350021, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2915 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2915 = true := by
  decide +kernel

theorem tot2915 : totK PA10K2 A10K2.t2915 = [0, 560720091650, 1868781552326, 1721632150518, 421275093255, 24601572423, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

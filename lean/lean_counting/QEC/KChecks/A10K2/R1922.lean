import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7688 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7688 = true := by
  decide +kernel

theorem tot7688 : totK PA10K2 A10K2.t7688 = [0, 0, 0, 212799298291, 780129560516, 1625153364516, 1693020250695, 552313346896, 43324002404, 0] := by
  decide +kernel

theorem rows7689 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7689 = true := by
  decide +kernel

theorem tot7689 : totK PA10K2 A10K2.t7689 = [0, 0, 0, 481250890058, 1799052133348, 1901569182954, 526989621911, 32846090165, 0, 0] := by
  decide +kernel

theorem rows7690 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7690 = true := by
  decide +kernel

theorem tot7690 : totK PA10K2 A10K2.t7690 = [0, 0, 0, 350621537624, 1678625544456, 2153821702943, 722127891047, 46463430765, 0, 0] := by
  decide +kernel

theorem rows7691 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7691 = true := by
  decide +kernel

theorem tot7691 : totK PA10K2 A10K2.t7691 = [0, 0, 0, 171985178779, 1074842982193, 2094832375853, 1199616075465, 178672102858, 6034215561, 0] := by
  decide +kernel

end QECKChecks.A10K2

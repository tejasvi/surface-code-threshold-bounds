import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7964 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7964 = true := by
  decide +kernel

theorem tot7964 : totK PA10K2 A10K2.t7964 = [0, 0, 0, 499288224460, 1916119692870, 2060852516602, 544063168452, 18770739859, 0, 0] := by
  decide +kernel

theorem rows7965 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7965 = true := by
  decide +kernel

theorem tot7965 : totK PA10K2 A10K2.t7965 = [0, 0, 0, 512224944575, 1767332792331, 1818881270520, 624831475008, 56197020373, 0, 0] := by
  decide +kernel

theorem rows7966 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7966 = true := by
  decide +kernel

theorem tot7966 : totK PA10K2 A10K2.t7966 = [0, 0, 0, 295824282370, 1506021854777, 2215570699377, 844613596939, 53715700381, 0, 0] := by
  decide +kernel

theorem rows7967 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7967 = true := by
  decide +kernel

theorem tot7967 : totK PA10K2 A10K2.t7967 = [0, 0, 0, 230991879340, 1116019261464, 1973076843989, 1251352578588, 220569840491, 7151180950, 0] := by
  decide +kernel

end QECKChecks.A10K2

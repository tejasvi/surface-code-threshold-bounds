import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows964 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t964 = true := by
  decide +kernel

theorem tot964 : totK PA10K2 A10K2.t964 = [0, 0, 613336125721, 2060693688501, 1753132182966, 402124572652, 25351274858, 0, 0, 0] := by
  decide +kernel

theorem rows965 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t965 = true := by
  decide +kernel

theorem tot965 : totK PA10K2 A10K2.t965 = [0, 336129564531, 1325879486258, 1986987645798, 1119065934376, 178829764475, 5459593153, 0, 0, 0] := by
  decide +kernel

theorem rows966 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t966 = true := by
  decide +kernel

theorem tot966 : totK PA10K2 A10K2.t966 = [0, 222352777693, 1276902368051, 2116275131502, 1203693732762, 188488446769, 9236763341, 0, 0, 0] := by
  decide +kernel

theorem rows967 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t967 = true := by
  decide +kernel

theorem tot967 : totK PA10K2 A10K2.t967 = [0, 286185292359, 1335982166615, 2024970559117, 1144064838576, 215091497212, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

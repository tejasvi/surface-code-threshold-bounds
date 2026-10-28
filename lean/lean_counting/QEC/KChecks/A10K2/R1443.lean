import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5772 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5772 = true := by
  decide +kernel

theorem tot5772 : totK PA10K2 A10K2.t5772 = [0, 0, 526179114281, 1794320074178, 1849262703209, 527253836411, 32040661968, 0, 0, 0] := by
  decide +kernel

theorem rows5773 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5773 = true := by
  decide +kernel

theorem tot5773 : totK PA10K2 A10K2.t5773 = [0, 0, 0, 725994121114, 2077911068687, 1589139272664, 369242467233, 25371180993, 0, 0] := by
  decide +kernel

theorem rows5774 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5774 = true := by
  decide +kernel

theorem tot5774 : totK PA10K2 A10K2.t5774 = [0, 0, 237787317315, 1054260944871, 1897163508396, 1286019435053, 202100318255, 5460492893, 0, 0] := by
  decide +kernel

theorem rows5775 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5775 = true := by
  decide +kernel

theorem tot5775 : totK PA10K2 A10K2.t5775 = [0, 0, 466307234920, 1666633587295, 1865945752914, 636832143596, 51782903379, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

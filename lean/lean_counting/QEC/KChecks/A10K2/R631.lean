import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2524 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2524 = true := by
  decide +kernel

theorem tot2524 : totK PA10K2 A10K2.t2524 = [0, 0, 652303639716, 2087298968336, 1907806868233, 424804802900, 12224107035, 0, 0, 0] := by
  decide +kernel

theorem rows2525 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2525 = true := by
  decide +kernel

theorem tot2525 : totK PA10K2 A10K2.t2525 = [0, 319639362920, 1090297410176, 1588587930825, 1398544571075, 523887276349, 48886019071, 0, 0, 0] := by
  decide +kernel

theorem rows2526 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2526 = true := by
  decide +kernel

theorem tot2526 : totK PA10K2 A10K2.t2526 = [0, 538071541683, 1933365463325, 1918715922212, 422861024112, 12129354050, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2527 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2527 = true := by
  decide +kernel

theorem tot2527 : totK PA10K2 A10K2.t2527 = [0, 0, 669602610776, 2063588550853, 1697200955198, 395350733627, 25734533292, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows448 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t448 = true := by
  decide +kernel

theorem tot448 : totK PA10K2 A10K2.t448 = [0, 0, 283918886597, 1534093604956, 2039939199042, 633086523615, 44657785468, 0, 0, 0] := by
  decide +kernel

theorem rows449 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t449 = true := by
  decide +kernel

theorem tot449 : totK PA10K2 A10K2.t449 = [0, 0, 295159534809, 1264833493133, 1882540975146, 965639940376, 157363348910, 5528811039, 0, 0] := by
  decide +kernel

theorem rows450 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t450 = true := by
  decide +kernel

theorem tot450 : totK PA10K2 A10K2.t450 = [0, 115487560146, 685164955872, 1768046244082, 1924896136818, 577088282295, 43911449185, 0, 0, 0] := by
  decide +kernel

theorem rows451 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t451 = true := by
  decide +kernel

theorem tot451 : totK PA10K2 A10K2.t451 = [0, 467308048258, 1813271660595, 1990810695830, 502785989144, 25686058060, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4416 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4416 = true := by
  decide +kernel

theorem tot4416 : totK PA10K2 A10K2.t4416 = [0, 0, 0, 566013654771, 1838677263858, 1741623278325, 445729762336, 31193351345, 0, 0] := by
  decide +kernel

theorem rows4417 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4417 = true := by
  decide +kernel

theorem tot4417 : totK PA10K2 A10K2.t4417 = [0, 0, 0, 742734873431, 2198420064468, 1467692884973, 250315523575, 6354609102, 0, 0] := by
  decide +kernel

theorem rows4418 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4418 = true := by
  decide +kernel

theorem tot4418 : totK PA10K2 A10K2.t4418 = [0, 0, 0, 535468045052, 1819596422456, 1710585780134, 445476204503, 30559085710, 0, 0] := by
  decide +kernel

theorem rows4419 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4419 = true := by
  decide +kernel

theorem tot4419 : totK PA10K2 A10K2.t4419 = [0, 0, 0, 76234385009, 1316673099270, 2244857900412, 837610849025, 63831856235, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

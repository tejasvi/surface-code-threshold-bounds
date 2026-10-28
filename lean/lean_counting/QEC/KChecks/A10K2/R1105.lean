import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4420 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4420 = true := by
  decide +kernel

theorem tot4420 : totK PA10K2 A10K2.t4420 = [0, 421744910736, 1403430863362, 1385893616031, 413861852958, 464317055368, 533592381286, 129424075521, 5976421810, 0] := by
  decide +kernel

theorem rows4421 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4421 = true := by
  decide +kernel

theorem tot4421 : totK PA10K2 A10K2.t4421 = [0, 419155855408, 1695810862788, 1973134836548, 707953756572, 56291294061, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4422 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4422 = true := by
  decide +kernel

theorem tot4422 : totK PA10K2 A10K2.t4422 = [0, 0, 501509451288, 1908535768567, 1760674560679, 419352914461, 25371180993, 0, 0, 0] := by
  decide +kernel

theorem rows4423 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4423 = true := by
  decide +kernel

theorem tot4423 : totK PA10K2 A10K2.t4423 = [0, 352873183950, 1424607474711, 1983775299734, 996749323894, 159318898413, 5460492893, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows860 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t860 = true := by
  decide +kernel

theorem tot860 : totK PA10K2 A10K2.t860 = [0, 446685053060, 1741916113809, 1919264491104, 520132453562, 31222411477, 0, 0, 0, 0] := by
  decide +kernel

theorem rows861 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t861 = true := by
  decide +kernel

theorem tot861 : totK PA10K2 A10K2.t861 = [0, 255541832339, 1340537744474, 2116709617904, 1083831273577, 175405115111, 14945844243, 0, 0, 0] := by
  decide +kernel

theorem rows862 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t862 = true := by
  decide +kernel

theorem tot862 : totK PA10K2 A10K2.t862 = [0, 149371390269, 820159056669, 1781799109288, 1464323007010, 372591730309, 15704651987, 0, 0, 0] := by
  decide +kernel

theorem rows863 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t863 = true := by
  decide +kernel

theorem tot863 : totK PA10K2 A10K2.t863 = [0, 326995199175, 1592085102054, 2104463675502, 726058291155, 52556790262, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

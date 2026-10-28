import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5948 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5948 = true := by
  decide +kernel

theorem tot5948 : totK PA10K2 A10K2.t5948 = [0, 166722870884, 931574937442, 1932989587156, 1254574310866, 179289924005, 5705019915, 0, 0, 0] := by
  decide +kernel

theorem rows5949 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5949 = true := by
  decide +kernel

theorem tot5949 : totK PA10K2 A10K2.t5949 = [0, 557553851768, 1958538748839, 2000302457775, 548069211628, 32495405313, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5950 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5950 = true := by
  decide +kernel

theorem tot5950 : totK PA10K2 A10K2.t5950 = [0, 61859181966, 882370860124, 2185575571432, 1620115582436, 285036162293, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows5951 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5951 = true := by
  decide +kernel

theorem tot5951 : totK PA10K2 A10K2.t5951 = [0, 0, 655633266069, 2084471732754, 1770201841661, 444357717794, 28177825909, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

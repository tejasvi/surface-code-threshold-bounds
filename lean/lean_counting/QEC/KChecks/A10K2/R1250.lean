import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5000 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5000 = true := by
  decide +kernel

theorem tot5000 : totK PA10K2 A10K2.t5000 = [0, 1083936530857, 2428525477153, 1157966060381, 93642610035, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5001 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5001 = true := by
  decide +kernel

theorem tot5001 : totK PA10K2 A10K2.t5001 = [0, 464016627211, 1829349649371, 1841740793878, 507527251348, 31987755669, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5002 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5002 = true := by
  decide +kernel

theorem tot5002 : totK PA10K2 A10K2.t5002 = [0, 561997148270, 1920379925002, 1883097311252, 456820748885, 13149912228, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5003 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5003 = true := by
  decide +kernel

theorem tot5003 : totK PA10K2 A10K2.t5003 = [0, 463415452603, 1848982029708, 1933001495505, 473833402402, 26116334861, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

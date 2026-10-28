import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2768 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2768 = true := by
  decide +kernel

theorem tot2768 : totK PA10K2 A10K2.t2768 = [0, 526397487994, 1818593915241, 1893696789203, 513544589604, 31222411477, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2769 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2769 = true := by
  decide +kernel

theorem tot2769 : totK PA10K2 A10K2.t2769 = [0, 0, 819134434609, 2121089149303, 1494757854363, 359204035189, 25239774317, 0, 0, 0] := by
  decide +kernel

theorem rows2770 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2770 = true := by
  decide +kernel

theorem tot2770 : totK PA10K2 A10K2.t2770 = [0, 290969025496, 1225997276980, 1850528752706, 1141990788445, 190598885651, 5410721913, 0, 0, 0] := by
  decide +kernel

theorem rows2771 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2771 = true := by
  decide +kernel

theorem tot2771 : totK PA10K2 A10K2.t2771 = [0, 267455241510, 1436922292573, 2143548794803, 801972695664, 58581722383, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

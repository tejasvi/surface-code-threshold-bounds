import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6400 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6400 = true := by
  decide +kernel

theorem tot6400 : totK PA10K2 A10K2.t6400 = [0, 655145130093, 2180505983978, 1929315772721, 365867933944, 6853348008, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6401 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6401 = true := by
  decide +kernel

theorem tot6401 : totK PA10K2 A10K2.t6401 = [0, 515752820698, 1796524824321, 1995023851009, 707161591502, 56126419230, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6402 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6402 = true := by
  decide +kernel

theorem tot6402 : totK PA10K2 A10K2.t6402 = [0, 580747034572, 1949523135246, 1909556481656, 499368365509, 31222411477, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6403 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6403 = true := by
  decide +kernel

theorem tot6403 : totK PA10K2 A10K2.t6403 = [0, 0, 782863293836, 2140433005857, 1517964775279, 365476556930, 25239774317, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6908 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6908 = true := by
  decide +kernel

theorem tot6908 : totK PA10K2 A10K2.t6908 = [0, 0, 306392981073, 1406997683325, 2146145654383, 1092544512473, 104791477108, 0, 0, 0] := by
  decide +kernel

theorem rows6909 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6909 = true := by
  decide +kernel

theorem tot6909 : totK PA10K2 A10K2.t6909 = [0, 0, 286110476401, 1290430199515, 2000524553208, 1195367147508, 187521079741, 6766355402, 0, 0] := by
  decide +kernel

theorem rows6910 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6910 = true := by
  decide +kernel

theorem tot6910 : totK PA10K2 A10K2.t6910 = [0, 0, 581583812515, 1959759149410, 1918170117383, 489406591411, 18186494405, 0, 0, 0] := by
  decide +kernel

theorem rows6911 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6911 = true := by
  decide +kernel

theorem tot6911 : totK PA10K2 A10K2.t6911 = [0, 0, 0, 757143998614, 2233190869351, 1679038654423, 255446519339, 6066958478, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

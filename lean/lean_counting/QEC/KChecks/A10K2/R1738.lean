import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6952 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6952 = true := by
  decide +kernel

theorem tot6952 : totK PA10K2 A10K2.t6952 = [0, 0, 487858484474, 1680935779541, 1831833805361, 801965500327, 149677818240, 5885702948, 0, 0] := by
  decide +kernel

theorem rows6953 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6953 = true := by
  decide +kernel

theorem tot6953 : totK PA10K2 A10K2.t6953 = [0, 209557633364, 831923358958, 1523212738406, 1688547795135, 678339546884, 55961573029, 0, 0, 0] := by
  decide +kernel

theorem rows6954 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6954 = true := by
  decide +kernel

theorem tot6954 : totK PA10K2 A10K2.t6954 = [0, 485218252816, 1797719482650, 2001271146393, 571608458804, 32846095359, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6955 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6955 = true := by
  decide +kernel

theorem tot6955 : totK PA10K2 A10K2.t6955 = [0, 67940916035, 837960474289, 2049128433318, 1613019792508, 386572646858, 25734533292, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

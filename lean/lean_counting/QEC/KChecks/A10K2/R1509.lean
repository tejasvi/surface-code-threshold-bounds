import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6036 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6036 = true := by
  decide +kernel

theorem tot6036 : totK PA10K2 A10K2.t6036 = [0, 286318995780, 1198315523709, 1800924052531, 1112585638289, 190447083892, 5410721913, 0, 0, 0] := by
  decide +kernel

theorem rows6037 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6037 = true := by
  decide +kernel

theorem tot6037 : totK PA10K2 A10K2.t6037 = [0, 231940221735, 1395075453170, 2143763343537, 799824606201, 58581722383, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6038 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6038 = true := by
  decide +kernel

theorem tot6038 : totK PA10K2 A10K2.t6038 = [0, 293840244305, 1232587528414, 1875497721909, 1077991811719, 180120650298, 5546304973, 0, 0, 0] := by
  decide +kernel

theorem rows6039 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6039 = true := by
  decide +kernel

theorem tot6039 : totK PA10K2 A10K2.t6039 = [0, 526330773538, 1947619010331, 2158139139965, 587436511517, 19876255495, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

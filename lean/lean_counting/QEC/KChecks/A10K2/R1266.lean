import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5064 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5064 = true := by
  decide +kernel

theorem tot5064 : totK PA10K2 A10K2.t5064 = [0, 464557879428, 1827423449438, 2078064240841, 579154403942, 23443334878, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5065 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5065 = true := by
  decide +kernel

theorem tot5065 : totK PA10K2 A10K2.t5065 = [0, 0, 566576228012, 1992834889847, 1800487328583, 423974805468, 25351274858, 0, 0, 0] := by
  decide +kernel

theorem rows5066 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5066 = true := by
  decide +kernel

theorem tot5066 : totK PA10K2 A10K2.t5066 = [0, 390797214289, 1499327677706, 1947414198872, 975364037105, 164482287984, 5459593153, 0, 0, 0] := by
  decide +kernel

theorem rows5067 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5067 = true := by
  decide +kernel

theorem tot5067 : totK PA10K2 A10K2.t5067 = [0, 202394752813, 1216315205869, 2172842299330, 1287644213977, 201117997991, 6853348008, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

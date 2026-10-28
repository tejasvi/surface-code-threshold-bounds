import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1372 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1372 = true := by
  decide +kernel

theorem tot1372 : totK PA10K2 A10K2.t1372 = [0, 0, 0, 579166007354, 1989399863980, 1763210132423, 412859251326, 25371180993, 0, 0] := by
  decide +kernel

theorem rows1373 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1373 = true := by
  decide +kernel

theorem tot1373 : totK PA10K2 A10K2.t1373 = [0, 0, 425141663883, 1490619263932, 1659735045066, 904478071452, 165730435067, 5460492893, 0, 0] := by
  decide +kernel

theorem rows1374 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1374 = true := by
  decide +kernel

theorem tot1374 : totK PA10K2 A10K2.t1374 = [0, 0, 147676090664, 984425270183, 2046094170058, 1164847963641, 139529820925, 6034215561, 0, 0] := by
  decide +kernel

theorem rows1375 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t1375 = true := by
  decide +kernel

theorem tot1375 : totK PA10K2 A10K2.t1375 = [0, 0, 427540798553, 1667154684684, 1866440875587, 574543510020, 37026429097, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

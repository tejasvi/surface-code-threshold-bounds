import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7296 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7296 = true := by
  decide +kernel

theorem tot7296 : totK PA10K2 A10K2.t7296 = [0, 0, 441777860914, 1786434903215, 2026737884391, 551311243475, 16148914787, 0, 0, 0] := by
  decide +kernel

theorem rows7297 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7297 = true := by
  decide +kernel

theorem tot7297 : totK PA10K2 A10K2.t7297 = [0, 0, 0, 576339752229, 1975021581520, 1738647943893, 419239122480, 25371180993, 0, 0] := by
  decide +kernel

theorem rows7298 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7298 = true := by
  decide +kernel

theorem tot7298 : totK PA10K2 A10K2.t7298 = [0, 0, 293873915135, 1278187233468, 1944645119790, 1140607678767, 189238650182, 5460492893, 0, 0] := by
  decide +kernel

theorem rows7299 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7299 = true := by
  decide +kernel

theorem tot7299 : totK PA10K2 A10K2.t7299 = [0, 0, 388194435581, 1618598610182, 1856116177010, 556866479360, 38188255074, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows892 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t892 = true := by
  decide +kernel

theorem tot892 : totK PA10K2 A10K2.t892 = [0, 280981490432, 1294385197175, 1928696143399, 1193465655986, 221996818585, 7047025452, 0, 0, 0] := by
  decide +kernel

theorem rows893 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t893 = true := by
  decide +kernel

theorem tot893 : totK PA10K2 A10K2.t893 = [0, 564985100011, 1832035044135, 1906443764498, 570395844420, 23620721234, 0, 0, 0, 0] := by
  decide +kernel

theorem rows894 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t894 = true := by
  decide +kernel

theorem tot894 : totK PA10K2 A10K2.t894 = [0, 46039240014, 936158851514, 2207677707838, 1535291695984, 244681154939, 6066958478, 0, 0, 0] := by
  decide +kernel

theorem rows895 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t895 = true := by
  decide +kernel

theorem tot895 : totK PA10K2 A10K2.t895 = [0, 0, 508986020566, 1931495330076, 1984087360161, 496532528531, 17732757243, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

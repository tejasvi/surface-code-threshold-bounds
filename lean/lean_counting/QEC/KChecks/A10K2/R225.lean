import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows900 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t900 = true := by
  decide +kernel

theorem tot900 : totK PA10K2 A10K2.t900 = [0, 218062639411, 1111446101592, 1977146634675, 1189856217491, 181117612226, 5705019915, 0, 0, 0] := by
  decide +kernel

theorem rows901 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t901 = true := by
  decide +kernel

theorem tot901 : totK PA10K2 A10K2.t901 = [0, 513579596073, 1921133179528, 2064548121816, 596671255982, 37396946132, 0, 0, 0, 0] := by
  decide +kernel

theorem rows902 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t902 = true := by
  decide +kernel

theorem tot902 : totK PA10K2 A10K2.t902 = [0, 67940784783, 897394144038, 2155458360659, 1620799629097, 295282502051, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows903 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t903 = true := by
  decide +kernel

theorem tot903 : totK PA10K2 A10K2.t903 = [0, 0, 508428074449, 1941661222176, 2125996894259, 560820502295, 18183661895, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

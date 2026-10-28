import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4928 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4928 = true := by
  decide +kernel

theorem tot4928 : totK PA10K2 A10K2.t4928 = [0, 337400259641, 1586108452365, 2145330894986, 830005501556, 70655796588, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4929 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4929 = true := by
  decide +kernel

theorem tot4929 : totK PA10K2 A10K2.t4929 = [0, 187476707758, 1033181176487, 1994248985257, 1438635710990, 256369089894, 7047025452, 0, 0, 0] := by
  decide +kernel

theorem rows4930 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4930 = true := by
  decide +kernel

theorem tot4930 : totK PA10K2 A10K2.t4930 = [0, 407759875301, 1713480739430, 2188339602519, 770617906505, 36915635290, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4931 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4931 = true := by
  decide +kernel

theorem tot4931 : totK PA10K2 A10K2.t4931 = [0, 0, 587922146439, 2027903159718, 1946190678132, 449817968724, 11910457242, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3040 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3040 = true := by
  decide +kernel

theorem tot3040 : totK PA10K2 A10K2.t3040 = [0, 42959446034, 360327863534, 1503904173803, 2146535650188, 890535957058, 76351749596, 0, 0, 0] := by
  decide +kernel

theorem rows3041 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3041 = true := by
  decide +kernel

theorem tot3041 : totK PA10K2 A10K2.t3041 = [0, 532884204012, 1944037207086, 1908933080081, 480732925161, 26491486257, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3042 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3042 = true := by
  decide +kernel

theorem tot3042 : totK PA10K2 A10K2.t3042 = [0, 220651030548, 1223616999155, 2184888749694, 1253369043698, 193734261991, 15171143123, 0, 0, 0] := by
  decide +kernel

theorem rows3043 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3043 = true := by
  decide +kernel

theorem tot3043 : totK PA10K2 A10K2.t3043 = [0, 102577054862, 691444834761, 1863934670740, 1740276748135, 408014377500, 16372646742, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2

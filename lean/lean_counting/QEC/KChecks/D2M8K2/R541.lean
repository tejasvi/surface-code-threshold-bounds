import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2164 = true := by
  decide +kernel

theorem tot2164 : totK PD2M8K2 D2M8K2.t2164 = [0, 0, 0, 359505919913, 477801201401, 52864869152, 0, 0] := by
  decide +kernel

theorem rows2165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2165 = true := by
  decide +kernel

theorem tot2165 : totK PD2M8K2 D2M8K2.t2165 = [0, 126877611947, 281934289431, 186204873970, 223022953957, 76579227072, 1415142070, 0] := by
  decide +kernel

theorem rows2166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2166 = true := by
  decide +kernel

theorem tot2166 : totK PD2M8K2 D2M8K2.t2166 = [0, 192720305274, 453690834722, 224303141588, 17111991321, 0, 0, 0] := by
  decide +kernel

theorem rows2167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2167 = true := by
  decide +kernel

theorem tot2167 : totK PD2M8K2 D2M8K2.t2167 = [0, 82817439278, 395679439196, 355915949920, 45786070010, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1388 = true := by
  decide +kernel

theorem tot1388 : totK PD2M8K2 D2M8K2.t1388 = [0, 93968110056, 292894479301, 350456470551, 156927558651, 8191853852, 0, 0] := by
  decide +kernel

theorem rows1389 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1389 = true := by
  decide +kernel

theorem tot1389 : totK PD2M8K2 D2M8K2.t1389 = [0, 166391645637, 436484741723, 275056545394, 30366358905, 0, 0, 0] := by
  decide +kernel

theorem rows1390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1390 = true := by
  decide +kernel

theorem tot1390 : totK PD2M8K2 D2M8K2.t1390 = [0, 142895473479, 448385570719, 287204710718, 25140317429, 0, 0, 0] := by
  decide +kernel

theorem rows1391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1391 = true := by
  decide +kernel

theorem tot1391 : totK PD2M8K2 D2M8K2.t1391 = [0, 0, 214433686563, 488689860126, 180044525023, 7877773091, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

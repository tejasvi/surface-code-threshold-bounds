import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11000 = true := by
  decide +kernel

theorem tot11000 : totK PD2M8K2 D2M8K2.t11000 = [0, 196440643814, 471751630840, 215989057366, 12183533023, 0, 0, 0] := by
  decide +kernel

theorem rows11001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11001 = true := by
  decide +kernel

theorem tot11001 : totK PD2M8K2 D2M8K2.t11001 = [0, 31996086117, 324330008943, 426235185081, 84814258277, 1162935789, 0, 0] := by
  decide +kernel

theorem rows11002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11002 = true := by
  decide +kernel

theorem tot11002 : totK PD2M8K2 D2M8K2.t11002 = [0, 0, 198554860649, 453814077719, 184002545955, 11853261585, 0, 0] := by
  decide +kernel

theorem rows11003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11003 = true := by
  decide +kernel

theorem tot11003 : totK PD2M8K2 D2M8K2.t11003 = [0, 164100838655, 458158848206, 254650426463, 20904009581, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

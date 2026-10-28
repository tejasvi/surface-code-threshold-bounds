import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4976 = true := by
  decide +kernel

theorem tot4976 : totK PD2M8K2 D2M8K2.t4976 = [0, 30064243916, 339745681347, 445032916554, 85125594966, 1096156699, 0, 0] := by
  decide +kernel

theorem rows4977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4977 = true := by
  decide +kernel

theorem tot4977 : totK PD2M8K2 D2M8K2.t4977 = [0, 38071542638, 289111646099, 458679480066, 118897132941, 3880716147, 0, 0] := by
  decide +kernel

theorem rows4978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4978 = true := by
  decide +kernel

theorem tot4978 : totK PD2M8K2 D2M8K2.t4978 = [0, 181126971343, 448919040032, 274237601673, 28690938858, 0, 0, 0] := by
  decide +kernel

theorem rows4979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4979 = true := by
  decide +kernel

theorem tot4979 : totK PD2M8K2 D2M8K2.t4979 = [0, 126596237879, 443893778478, 321573915048, 34349790806, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

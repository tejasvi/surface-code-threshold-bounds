import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3008 = true := by
  decide +kernel

theorem tot3008 : totK PD2M8K2 D2M8K2.t3008 = [0, 134282421382, 357054915473, 312937087740, 91273979588, 3880716147, 0, 0] := by
  decide +kernel

theorem rows3009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3009 = true := by
  decide +kernel

theorem tot3009 : totK PD2M8K2 D2M8K2.t3009 = [0, 168160856144, 446551310622, 279284452196, 29322329664, 0, 0, 0] := by
  decide +kernel

theorem rows3010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3010 = true := by
  decide +kernel

theorem tot3010 : totK PD2M8K2 D2M8K2.t3010 = [0, 111042906525, 425167560008, 336453819909, 31538060220, 0, 0, 0] := by
  decide +kernel

theorem rows3011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3011 = true := by
  decide +kernel

theorem tot3011 : totK PD2M8K2 D2M8K2.t3011 = [0, 0, 227068835392, 487262936185, 169148623401, 4925188030, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

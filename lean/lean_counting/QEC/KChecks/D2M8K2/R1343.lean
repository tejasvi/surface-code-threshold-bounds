import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5372 = true := by
  decide +kernel

theorem tot5372 : totK PD2M8K2 D2M8K2.t5372 = [0, 0, 97159877541, 395502161097, 336465520264, 47230549377, 1075657031, 0] := by
  decide +kernel

theorem rows5373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5373 = true := by
  decide +kernel

theorem tot5373 : totK PD2M8K2 D2M8K2.t5373 = [0, 0, 0, 269358450135, 477752276142, 115214275572, 3804183361, 0] := by
  decide +kernel

theorem rows5374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5374 = true := by
  decide +kernel

theorem tot5374 : totK PD2M8K2 D2M8K2.t5374 = [0, 0, 170612615039, 450928178271, 255205278909, 28741055459, 0, 0] := by
  decide +kernel

theorem rows5375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5375 = true := by
  decide +kernel

theorem tot5375 : totK PD2M8K2 D2M8K2.t5375 = [0, 0, 164386082298, 437231540049, 263639073364, 19195537996, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

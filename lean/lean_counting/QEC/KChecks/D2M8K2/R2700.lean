import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10800 = true := by
  decide +kernel

theorem tot10800 : totK PD2M8K2 D2M8K2.t10800 = [0, 175186659058, 450236887209, 261346006083, 22300035540, 0, 0, 0] := by
  decide +kernel

theorem rows10801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10801 = true := by
  decide +kernel

theorem tot10801 : totK PD2M8K2 D2M8K2.t10801 = [0, 173395568718, 480182345548, 248774431817, 11187970797, 0, 0, 0] := by
  decide +kernel

theorem rows10802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10802 = true := by
  decide +kernel

theorem tot10802 : totK PD2M8K2 D2M8K2.t10802 = [0, 0, 180457771676, 453584573754, 247475482132, 24261412795, 0, 0] := by
  decide +kernel

theorem rows10803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10803 = true := by
  decide +kernel

theorem tot10803 : totK PD2M8K2 D2M8K2.t10803 = [0, 0, 204876805712, 490753455198, 201545924242, 6543040663, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

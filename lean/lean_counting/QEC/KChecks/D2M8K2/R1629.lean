import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6516 = true := by
  decide +kernel

theorem tot6516 : totK PD2M8K2 D2M8K2.t6516 = [0, 164803508387, 453190913949, 267503090969, 25357676561, 0, 0, 0] := by
  decide +kernel

theorem rows6517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6517 = true := by
  decide +kernel

theorem tot6517 : totK PD2M8K2 D2M8K2.t6517 = [0, 167657833767, 484606032284, 235760037676, 7641798031, 0, 0, 0] := by
  decide +kernel

theorem rows6518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6518 = true := by
  decide +kernel

theorem tot6518 : totK PD2M8K2 D2M8K2.t6518 = [175244447038, 449537067089, 247134148434, 38622842891, 4414412796, 0, 0, 0] := by
  decide +kernel

theorem rows6519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6519 = true := by
  decide +kernel

theorem tot6519 : totK PD2M8K2 D2M8K2.t6519 = [194554700486, 478230189546, 223392625679, 12373752831, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

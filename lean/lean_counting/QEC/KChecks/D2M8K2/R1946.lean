import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7784 = true := by
  decide +kernel

theorem tot7784 : totK PD2M8K2 D2M8K2.t7784 = [0, 160979367222, 456031060724, 269425050687, 24599451881, 0, 0, 0] := by
  decide +kernel

theorem rows7785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7785 = true := by
  decide +kernel

theorem tot7785 : totK PD2M8K2 D2M8K2.t7785 = [0, 165316035488, 457523081590, 251150329792, 18471403130, 0, 0, 0] := by
  decide +kernel

theorem rows7786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7786 = true := by
  decide +kernel

theorem tot7786 : totK PD2M8K2 D2M8K2.t7786 = [0, 0, 226952504909, 499189670129, 159947345310, 7166294683, 0, 0] := by
  decide +kernel

theorem rows7787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7787 = true := by
  decide +kernel

theorem tot7787 : totK PD2M8K2 D2M8K2.t7787 = [0, 86311067613, 288744746313, 374982687022, 121518949582, 5883432551, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

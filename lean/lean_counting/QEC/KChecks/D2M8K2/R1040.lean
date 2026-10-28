import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4160 = true := by
  decide +kernel

theorem tot4160 : totK PD2M8K2 D2M8K2.t4160 = [0, 204313739261, 490514727047, 201604315687, 8421995651, 0, 0, 0] := by
  decide +kernel

theorem rows4161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4161 = true := by
  decide +kernel

theorem tot4161 : totK PD2M8K2 D2M8K2.t4161 = [0, 88786514364, 407567240709, 371175283752, 36702204085, 0, 0, 0] := by
  decide +kernel

theorem rows4162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4162 = true := by
  decide +kernel

theorem tot4162 : totK PD2M8K2 D2M8K2.t4162 = [0, 93610018881, 389249339577, 401474229941, 48199182100, 0, 0, 0] := by
  decide +kernel

theorem rows4163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4163 = true := by
  decide +kernel

theorem tot4163 : totK PD2M8K2 D2M8K2.t4163 = [0, 174769799367, 438585918513, 266945251599, 30239336881, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

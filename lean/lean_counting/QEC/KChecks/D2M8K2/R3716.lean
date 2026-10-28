import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14864 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14864 = true := by
  decide +kernel

theorem tot14864 : totK PD2M8K2 D2M8K2.t14864 = [0, 164685770815, 446057537378, 278834439479, 27190566548, 0, 0, 0] := by
  decide +kernel

theorem rows14865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14865 = true := by
  decide +kernel

theorem tot14865 : totK PD2M8K2 D2M8K2.t14865 = [0, 125366172592, 430939266445, 305378744410, 25003604383, 0, 0, 0] := by
  decide +kernel

theorem rows14866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14866 = true := by
  decide +kernel

theorem tot14866 : totK PD2M8K2 D2M8K2.t14866 = [0, 0, 214391096595, 473833560178, 175990669833, 9633262574, 0, 0] := by
  decide +kernel

theorem rows14867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14867 = true := by
  decide +kernel

theorem tot14867 : totK PD2M8K2 D2M8K2.t14867 = [0, 78938184031, 329566587008, 345539929193, 88256706514, 3472187823, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

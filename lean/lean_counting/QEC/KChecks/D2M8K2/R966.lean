import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3864 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3864 = true := by
  decide +kernel

theorem tot3864 : totK PD2M8K2 D2M8K2.t3864 = [0, 126419686420, 438929219066, 319241945687, 26940143319, 0, 0, 0] := by
  decide +kernel

theorem rows3865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3865 = true := by
  decide +kernel

theorem tot3865 : totK PD2M8K2 D2M8K2.t3865 = [0, 0, 228724250904, 478439229057, 155402399169, 4811815119, 0, 0] := by
  decide +kernel

theorem rows3866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3866 = true := by
  decide +kernel

theorem tot3866 : totK PD2M8K2 D2M8K2.t3866 = [0, 37283609705, 206542331563, 409550291448, 206507042741, 16939352947, 0, 0] := by
  decide +kernel

theorem rows3867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3867 = true := by
  decide +kernel

theorem tot3867 : totK PD2M8K2 D2M8K2.t3867 = [0, 199084338869, 478227660138, 207253836910, 9778478082, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

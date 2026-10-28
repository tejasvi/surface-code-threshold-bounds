import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13792 = true := by
  decide +kernel

theorem tot13792 : totK PD2M8K2 D2M8K2.t13792 = [68309133624, 304553499305, 409510444739, 109083509794, 3795168977, 0, 0, 0] := by
  decide +kernel

theorem rows13793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13793 = true := by
  decide +kernel

theorem tot13793 : totK PD2M8K2 D2M8K2.t13793 = [177843304831, 467772124315, 258766800119, 23097808385, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13794 = true := by
  decide +kernel

theorem tot13794 : totK PD2M8K2 D2M8K2.t13794 = [179781219229, 468708351546, 245743189713, 16604971367, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13795 = true := by
  decide +kernel

theorem tot13795 : totK PD2M8K2 D2M8K2.t13795 = [0, 282222738851, 506893624098, 117994215448, 1260002070, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

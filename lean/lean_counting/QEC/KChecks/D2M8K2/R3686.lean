import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14744 = true := by
  decide +kernel

theorem tot14744 : totK PD2M8K2 D2M8K2.t14744 = [53419841661, 336661081810, 407612069018, 76624098072, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows14745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14745 = true := by
  decide +kernel

theorem tot14745 : totK PD2M8K2 D2M8K2.t14745 = [87932767747, 341114126848, 362171863524, 92562296472, 3884009855, 0, 0, 0] := by
  decide +kernel

theorem rows14746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14746 = true := by
  decide +kernel

theorem tot14746 : totK PD2M8K2 D2M8K2.t14746 = [160539553595, 447167185171, 272845348118, 28560793684, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14747 = true := by
  decide +kernel

theorem tot14747 : totK PD2M8K2 D2M8K2.t14747 = [176175293989, 461544407462, 255423228952, 17951104518, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

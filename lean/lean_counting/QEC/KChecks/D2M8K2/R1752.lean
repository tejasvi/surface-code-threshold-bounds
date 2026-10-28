import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7008 = true := by
  decide +kernel

theorem tot7008 : totK PD2M8K2 D2M8K2.t7008 = [0, 0, 0, 274141647593, 462892608145, 118010634813, 4028038878, 0] := by
  decide +kernel

theorem rows7009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7009 = true := by
  decide +kernel

theorem tot7009 : totK PD2M8K2 D2M8K2.t7009 = [0, 0, 169795705981, 471204772049, 240027085653, 16964039254, 0, 0] := by
  decide +kernel

theorem rows7010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7010 = true := by
  decide +kernel

theorem tot7010 : totK PD2M8K2 D2M8K2.t7010 = [0, 0, 198657166548, 460402839694, 220195169194, 13278482868, 0, 0] := by
  decide +kernel

theorem rows7011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7011 = true := by
  decide +kernel

theorem tot7011 : totK PD2M8K2 D2M8K2.t7011 = [0, 141987590768, 348023232598, 273010679304, 131264914350, 13566916688, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

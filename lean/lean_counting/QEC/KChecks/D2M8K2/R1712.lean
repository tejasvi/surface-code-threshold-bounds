import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6848 = true := by
  decide +kernel

theorem tot6848 : totK PD2M8K2 D2M8K2.t6848 = [0, 214717630082, 487605612057, 182824363791, 7439274334, 0, 0, 0] := by
  decide +kernel

theorem rows6849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6849 = true := by
  decide +kernel

theorem tot6849 : totK PD2M8K2 D2M8K2.t6849 = [0, 188446019973, 472408760699, 215024573035, 14703944056, 0, 0, 0] := by
  decide +kernel

theorem rows6850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6850 = true := by
  decide +kernel

theorem tot6850 : totK PD2M8K2 D2M8K2.t6850 = [0, 195036724273, 476415748977, 199241392503, 9713690252, 0, 0, 0] := by
  decide +kernel

theorem rows6851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6851 = true := by
  decide +kernel

theorem tot6851 : totK PD2M8K2 D2M8K2.t6851 = [0, 86921654167, 357384565275, 355659692528, 62433255781, 1239866073, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

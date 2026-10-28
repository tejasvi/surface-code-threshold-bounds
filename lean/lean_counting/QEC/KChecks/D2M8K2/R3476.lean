import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13904 = true := by
  decide +kernel

theorem tot13904 : totK PD2M8K2 D2M8K2.t13904 = [0, 170145566966, 445450391299, 261508280307, 29185766107, 0, 0, 0] := by
  decide +kernel

theorem rows13905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13905 = true := by
  decide +kernel

theorem tot13905 : totK PD2M8K2 D2M8K2.t13905 = [0, 197080242538, 494135171259, 207583002782, 10179897161, 0, 0, 0] := by
  decide +kernel

theorem rows13906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13906 = true := by
  decide +kernel

theorem tot13906 : totK PD2M8K2 D2M8K2.t13906 = [0, 174468135017, 466572858347, 248125802880, 16637597621, 0, 0, 0] := by
  decide +kernel

theorem rows13907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13907 = true := by
  decide +kernel

theorem tot13907 : totK PD2M8K2 D2M8K2.t13907 = [0, 177396333935, 470661160023, 231528178389, 10956148868, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

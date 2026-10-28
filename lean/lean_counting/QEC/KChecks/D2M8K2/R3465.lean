import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13860 = true := by
  decide +kernel

theorem tot13860 : totK PD2M8K2 D2M8K2.t13860 = [187979295013, 464541751872, 252481682567, 23178887848, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13861 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13861 = true := by
  decide +kernel

theorem tot13861 : totK PD2M8K2 D2M8K2.t13861 = [187817575418, 473383898479, 224174152679, 12523541424, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13862 = true := by
  decide +kernel

theorem tot13862 : totK PD2M8K2 D2M8K2.t13862 = [30583749538, 313470082630, 457501355832, 96757277495, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows13863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13863 = true := by
  decide +kernel

theorem tot13863 : totK PD2M8K2 D2M8K2.t13863 = [0, 197938971822, 467465527976, 193369778741, 12052611869, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

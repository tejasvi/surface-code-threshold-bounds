import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13020 = true := by
  decide +kernel

theorem tot13020 : totK PD2M8K2 D2M8K2.t13020 = [0, 0, 187309972821, 458598393029, 229501152131, 16702988424, 0, 0] := by
  decide +kernel

theorem rows13021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13021 = true := by
  decide +kernel

theorem tot13021 : totK PD2M8K2 D2M8K2.t13021 = [0, 0, 37461509409, 349012016143, 399531301976, 73682748921, 1095107716, 0] := by
  decide +kernel

theorem rows13022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13022 = true := by
  decide +kernel

theorem tot13022 : totK PD2M8K2 D2M8K2.t13022 = [0, 37084170812, 45764610505, 240955687908, 431539769421, 118532399241, 3882006667, 0] := by
  decide +kernel

theorem rows13023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13023 = true := by
  decide +kernel

theorem tot13023 : totK PD2M8K2 D2M8K2.t13023 = [0, 197461056636, 477715983543, 204221388288, 9845055932, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

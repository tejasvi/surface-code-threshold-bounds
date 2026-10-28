import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13892 = true := by
  decide +kernel

theorem tot13892 : totK PD2M8K2 D2M8K2.t13892 = [195347575968, 460364981781, 242592332773, 23259966184, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13893 = true := by
  decide +kernel

theorem tot13893 : totK PD2M8K2 D2M8K2.t13893 = [183628124413, 472639662649, 224322546899, 12373752831, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13894 = true := by
  decide +kernel

theorem tot13894 : totK PD2M8K2 D2M8K2.t13894 = [11346165650, 305608575114, 475676882857, 105324776577, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows13895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13895 = true := by
  decide +kernel

theorem tot13895 : totK PD2M8K2 D2M8K2.t13895 = [10390456553, 193316366697, 464093227477, 190311077395, 11885407614, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

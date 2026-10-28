import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14016 = true := by
  decide +kernel

theorem tot14016 : totK PD2M8K2 D2M8K2.t14016 = [0, 0, 197928222855, 466636757700, 216983736021, 11965265540, 0, 0] := by
  decide +kernel

theorem rows14017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14017 = true := by
  decide +kernel

theorem tot14017 : totK PD2M8K2 D2M8K2.t14017 = [0, 0, 188589328272, 469033045240, 228484083927, 16104584588, 0, 0] := by
  decide +kernel

theorem rows14018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14018 = true := by
  decide +kernel

theorem tot14018 : totK PD2M8K2 D2M8K2.t14018 = [0, 0, 188264953785, 463239257821, 215232690001, 12183533023, 0, 0] := by
  decide +kernel

theorem rows14019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14019 = true := by
  decide +kernel

theorem tot14019 : totK PD2M8K2 D2M8K2.t14019 = [0, 0, 19433589518, 378089068767, 443299291765, 49840081135, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2

Picinae_core.vo Picinae_core.glob Picinae_core.v.beautified Picinae_core.required_vo: Picinae_core.v 
Picinae_core.vio: Picinae_core.v 
Picinae_core.vos Picinae_core.vok Picinae_core.required_vos: Picinae_core.v 
Picinae_theory.vo Picinae_theory.glob Picinae_theory.v.beautified Picinae_theory.required_vo: Picinae_theory.v Picinae_core.vo
Picinae_theory.vio: Picinae_theory.v Picinae_core.vio
Picinae_theory.vos Picinae_theory.vok Picinae_theory.required_vos: Picinae_theory.v Picinae_core.vos
Picinae_statics.vo Picinae_statics.glob Picinae_statics.v.beautified Picinae_statics.required_vo: Picinae_statics.v Picinae_theory.vo
Picinae_statics.vio: Picinae_statics.v Picinae_theory.vio
Picinae_statics.vos Picinae_statics.vok Picinae_statics.required_vos: Picinae_statics.v Picinae_theory.vos
Picinae_finterp.vo Picinae_finterp.glob Picinae_finterp.v.beautified Picinae_finterp.required_vo: Picinae_finterp.v Picinae_statics.vo
Picinae_finterp.vio: Picinae_finterp.v Picinae_statics.vio
Picinae_finterp.vos Picinae_finterp.vok Picinae_finterp.required_vos: Picinae_finterp.v Picinae_statics.vos
Picinae_simplifier_base.vo Picinae_simplifier_base.glob Picinae_simplifier_base.v.beautified Picinae_simplifier_base.required_vo: Picinae_simplifier_base.v Picinae_core.vo Picinae_finterp.vo
Picinae_simplifier_base.vio: Picinae_simplifier_base.v Picinae_core.vio Picinae_finterp.vio
Picinae_simplifier_base.vos Picinae_simplifier_base.vok Picinae_simplifier_base.required_vos: Picinae_simplifier_base.v Picinae_core.vos Picinae_finterp.vos
Picinae_simplifier_v1_0.vo Picinae_simplifier_v1_0.glob Picinae_simplifier_v1_0.v.beautified Picinae_simplifier_v1_0.required_vo: Picinae_simplifier_v1_0.v Picinae_core.vo Picinae_statics.vo Picinae_finterp.vo Picinae_simplifier_base.vo
Picinae_simplifier_v1_0.vio: Picinae_simplifier_v1_0.v Picinae_core.vio Picinae_statics.vio Picinae_finterp.vio Picinae_simplifier_base.vio
Picinae_simplifier_v1_0.vos Picinae_simplifier_v1_0.vok Picinae_simplifier_v1_0.required_vos: Picinae_simplifier_v1_0.v Picinae_core.vos Picinae_statics.vos Picinae_finterp.vos Picinae_simplifier_base.vos
Picinae_simplifier_v1_1.vo Picinae_simplifier_v1_1.glob Picinae_simplifier_v1_1.v.beautified Picinae_simplifier_v1_1.required_vo: Picinae_simplifier_v1_1.v Picinae_core.vo Picinae_statics.vo Picinae_finterp.vo Picinae_simplifier_base.vo
Picinae_simplifier_v1_1.vio: Picinae_simplifier_v1_1.v Picinae_core.vio Picinae_statics.vio Picinae_finterp.vio Picinae_simplifier_base.vio
Picinae_simplifier_v1_1.vos Picinae_simplifier_v1_1.vok Picinae_simplifier_v1_1.required_vos: Picinae_simplifier_v1_1.v Picinae_core.vos Picinae_statics.vos Picinae_finterp.vos Picinae_simplifier_base.vos
Picinae_i386.vo Picinae_i386.glob Picinae_i386.v.beautified Picinae_i386.required_vo: Picinae_i386.v Picinae_core.vo Picinae_theory.vo Picinae_statics.vo Picinae_finterp.vo Picinae_simplifier_v1_1.vo
Picinae_i386.vio: Picinae_i386.v Picinae_core.vio Picinae_theory.vio Picinae_statics.vio Picinae_finterp.vio Picinae_simplifier_v1_1.vio
Picinae_i386.vos Picinae_i386.vok Picinae_i386.required_vos: Picinae_i386.v Picinae_core.vos Picinae_theory.vos Picinae_statics.vos Picinae_finterp.vos Picinae_simplifier_v1_1.vos
Picinae_armv7.vo Picinae_armv7.glob Picinae_armv7.v.beautified Picinae_armv7.required_vo: Picinae_armv7.v Picinae_core.vo Picinae_theory.vo Picinae_statics.vo Picinae_finterp.vo Picinae_simplifier_v1_1.vo
Picinae_armv7.vio: Picinae_armv7.v Picinae_core.vio Picinae_theory.vio Picinae_statics.vio Picinae_finterp.vio Picinae_simplifier_v1_1.vio
Picinae_armv7.vos Picinae_armv7.vok Picinae_armv7.required_vos: Picinae_armv7.v Picinae_core.vos Picinae_theory.vos Picinae_statics.vos Picinae_finterp.vos Picinae_simplifier_v1_1.vos
Picinae_riscv.vo Picinae_riscv.glob Picinae_riscv.v.beautified Picinae_riscv.required_vo: Picinae_riscv.v Picinae_core.vo Picinae_theory.vo Picinae_statics.vo Picinae_finterp.vo Picinae_simplifier_v1_1.vo
Picinae_riscv.vio: Picinae_riscv.v Picinae_core.vio Picinae_theory.vio Picinae_statics.vio Picinae_finterp.vio Picinae_simplifier_v1_1.vio
Picinae_riscv.vos Picinae_riscv.vok Picinae_riscv.required_vos: Picinae_riscv.v Picinae_core.vos Picinae_theory.vos Picinae_statics.vos Picinae_finterp.vos Picinae_simplifier_v1_1.vos
Picinae_amd64.vo Picinae_amd64.glob Picinae_amd64.v.beautified Picinae_amd64.required_vo: Picinae_amd64.v Picinae_core.vo Picinae_theory.vo Picinae_statics.vo Picinae_finterp.vo Picinae_simplifier_v1_1.vo
Picinae_amd64.vio: Picinae_amd64.v Picinae_core.vio Picinae_theory.vio Picinae_statics.vio Picinae_finterp.vio Picinae_simplifier_v1_1.vio
Picinae_amd64.vos Picinae_amd64.vok Picinae_amd64.required_vos: Picinae_amd64.v Picinae_core.vos Picinae_theory.vos Picinae_statics.vos Picinae_finterp.vos Picinae_simplifier_v1_1.vos
